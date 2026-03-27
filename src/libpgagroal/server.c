/*
 * Copyright (C) 2026 The pgagroal community
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice, this list
 * of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice, this
 * list of conditions and the following disclaimer in the documentation and/or other
 * materials provided with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its contributors may
 * be used to endorse or promote products derived from this software without specific
 * prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
 * THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/* pgagroal */
#include <pgagroal.h>
#include <deque.h>
#include <logging.h>
#include <message.h>
#include <network.h>
#include <pool.h>
#include <security.h>
#include <server.h>
#include <utils.h>
#include <value.h>

/* system */
#include <errno.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>

static int failover(int old_primary);
static int process_server_parameters(int server, struct deque* server_parameters);
static int check_recovery_status(SSL* ssl, int socket, bool* in_recovery);
static int get_replication_lag(SSL* ssl, int socket, int64_t* lag_bytes);
static int get_auth_type(struct message* msg, int* auth_type);
static int wait_for_ready(SSL* ssl, int socket, struct message* initial_msg);
static int authenticate_direct_server(int server, SSL* ssl, int socket);

static int
get_auth_type(struct message* msg, int* auth_type)
{
   int offset = 0;
   char* data = NULL;

   *auth_type = -1;

   if (msg == NULL || msg->data == NULL || msg->length < 5)
   {
      return 1;
   }

   data = (char*)msg->data;

   while (offset <= (int)msg->length - 5)
   {
      char msg_type = data[offset];
      int32_t msg_len = pgagroal_read_int32(data + offset + 1);

      if (msg_type == 'R' && offset + 9 <= (int)msg->length)
      {
         *auth_type = pgagroal_read_int32(data + offset + 5);
         return 0;
      }

      if (msg_len <= 0)
      {
         break;
      }

      offset += 1 + msg_len;
   }

   return 1;
}

static int
wait_for_ready(SSL* ssl, int socket, struct message* initial_msg)
{
   int status;
   int rounds = 0;
   struct message* msg = NULL;
   unsigned char window[6];
   size_t window_len = 0;

   msg = initial_msg;
   memset(window, 0, sizeof(window));

   while (rounds++ < 32)
   {
      char* data = NULL;

      if (msg == NULL)
      {
         status = pgagroal_read_block_message(ssl, socket, &msg);
         if (status != MESSAGE_STATUS_OK)
         {
            pgagroal_clear_message(msg);
            return 1;
         }
      }

      data = (char*)msg->data;

      for (int i = 0; i < (int)msg->length; i++)
      {
         unsigned char b = (unsigned char)data[i];

         if (window_len < 6)
         {
            window[window_len++] = b;
         }
         else
         {
            memmove(window, window + 1, 5);
            window[5] = b;
         }

         if (window_len == 6)
         {
            signed char tx = (signed char)window[5];

            if (window[0] == 'Z' &&
                window[1] == 0 && window[2] == 0 && window[3] == 0 && window[4] == 5 &&
                (tx == 'I' || tx == 'T' || tx == 'E'))
            {
               if (msg != initial_msg)
               {
                  pgagroal_clear_message(msg);
               }
               return 0;
            }
         }
      }

      if (msg != initial_msg)
      {
         pgagroal_clear_message(msg);
      }
      msg = NULL;
   }

   return 1;
}

static int
authenticate_direct_server(int server __attribute__((unused)), SSL* ssl, int socket)
{
   int status;
   int auth_type;
   struct message* startup_msg = NULL;
   struct message* startup_response = NULL;
   struct message* auth_response = NULL;
   struct message* password_msg = NULL;
   struct main_configuration* config = (struct main_configuration*)shmem;

   status = pgagroal_create_startup_message(config->superuser.username, "postgres", &startup_msg);
   if (status != MESSAGE_STATUS_OK)
   {
      goto error;
   }

   status = pgagroal_write_message(ssl, socket, startup_msg);
   if (status != MESSAGE_STATUS_OK)
   {
      goto error;
   }

   status = pgagroal_read_block_message(ssl, socket, &startup_response);
   if (status != MESSAGE_STATUS_OK)
   {
      goto error;
   }

   if (get_auth_type(startup_response, &auth_type))
   {
      goto error;
   }

   if (auth_type == SECURITY_PASSWORD)
   {
      status = pgagroal_create_auth_password_response(config->superuser.password, &password_msg);
      if (status != MESSAGE_STATUS_OK)
      {
         goto error;
      }

      status = pgagroal_write_message(ssl, socket, password_msg);
      if (status != MESSAGE_STATUS_OK)
      {
         goto error;
      }

      status = pgagroal_read_block_message(ssl, socket, &auth_response);
      if (status != MESSAGE_STATUS_OK)
      {
         goto error;
      }

      if (get_auth_type(auth_response, &auth_type) || auth_type != SECURITY_TRUST)
      {
         goto error;
      }
   }
   else if (auth_type == SECURITY_MD5)
   {
      if (pgagroal_md5_client_auth(startup_response,
                                   config->superuser.username,
                                   config->superuser.password,
                                   socket,
                                   ssl,
                                   &auth_response) != AUTH_SUCCESS)
      {
         goto error;
      }
   }
   else if (auth_type == SECURITY_SCRAM256)
   {
      if (pgagroal_scram_client_auth(config->superuser.username,
                                     config->superuser.password,
                                     socket,
                                     ssl,
                                     &auth_response) != AUTH_SUCCESS)
      {
         goto error;
      }
   }
   else if (auth_type != SECURITY_TRUST)
   {
      goto error;
   }

   if (wait_for_ready(ssl, socket, (auth_response != NULL ? auth_response : startup_response)))
   {
      pgagroal_log_trace("auth_direct: wait_for_ready not observed, continuing");
   }

   pgagroal_free_message(startup_msg);
   pgagroal_clear_message(startup_response);
   pgagroal_clear_message(auth_response);
   pgagroal_free_message(password_msg);

   return 0;

error:
   pgagroal_free_message(startup_msg);
   pgagroal_clear_message(startup_response);
   pgagroal_clear_message(auth_response);
   pgagroal_free_message(password_msg);

   return 1;
}

/* TODO: extend with streaming replication info beyond pg_is_in_recovery(). */
static int
check_recovery_status(SSL* ssl, int socket, bool* in_recovery)
{
   int status;
   size_t size = 39;
   bool got_value = false;
   char is_recovery[size];
   struct message qmsg;
   struct message* tmsg = NULL;
   int rounds = 0;
   unsigned char frame_buf[65536];
   size_t frame_len = 0;

   *in_recovery = false;

   memset(&qmsg, 0, sizeof(struct message));
   memset(&is_recovery, 0, size);

   pgagroal_write_byte(&is_recovery, 'Q');
   pgagroal_write_int32(&(is_recovery[1]), size - 1);
   pgagroal_write_string(&(is_recovery[5]), "SELECT pg_is_in_recovery();");

   qmsg.kind = 'Q';
   qmsg.length = size;
   qmsg.data = &is_recovery;

   status = pgagroal_write_message(ssl, socket, &qmsg);
   if (status != MESSAGE_STATUS_OK)
   {
      goto error;
   }

   while (rounds++ < 16)
   {
      size_t offset = 0;

      status = pgagroal_read_block_message(ssl, socket, &tmsg);
      if (status != MESSAGE_STATUS_OK)
      {
         goto error;
      }

      if (frame_len + (size_t)tmsg->length > sizeof(frame_buf))
      {
         goto error;
      }

      memcpy(frame_buf + frame_len, tmsg->data, (size_t)tmsg->length);
      frame_len += (size_t)tmsg->length;

      while (frame_len - offset >= 5)
      {
         char msg_type = (char)frame_buf[offset];
         int32_t msg_len = pgagroal_read_int32((char*)frame_buf + offset + 1);
         size_t msg_size = (size_t)msg_len + 1;

         if (msg_len <= 0)
         {
            goto error;
         }

         if (frame_len - offset < msg_size)
         {
            break;
         }

         if (msg_type == 'D')
         {
            int16_t ncols = pgagroal_read_int16((char*)frame_buf + offset + 5);
            if (ncols >= 1)
            {
               size_t col_pos = offset + 7;
               int32_t col_len = pgagroal_read_int32((char*)frame_buf + col_pos);

               if (col_len > 0 && col_pos + 4 + (size_t)col_len <= offset + msg_size)
               {
                  signed char state = pgagroal_read_byte((char*)frame_buf + col_pos + 4);
                  *in_recovery = (state == 't');
                  got_value = true;
               }
            }
         }
         else if (msg_type == 'E')
         {
            goto error;
         }
         else if (msg_type == 'Z')
         {
            if (got_value)
            {
               pgagroal_clear_message(tmsg);
               return 0;
            }
         }

         offset += msg_size;
      }

      if (offset > 0)
      {
         memmove(frame_buf, frame_buf + offset, frame_len - offset);
         frame_len -= offset;
      }

      pgagroal_clear_message(tmsg);
      tmsg = NULL;
   }

   goto error;

error:
   pgagroal_clear_message(tmsg);
   return 1;
}

static int
get_replication_lag(SSL* ssl, int socket, int64_t* lag_bytes)
{
   int status;
   bool got_value = false;
   const char* query = "SELECT COALESCE(pg_wal_lsn_diff(pg_last_wal_receive_lsn(), pg_last_wal_replay_lsn()), 0)::bigint;";
   size_t qlen = strlen(query) + 1;
   size_t msglen = 1 + 4 + qlen;
   char* buf = NULL;
   struct message qmsg;
   struct message* tmsg = NULL;
   char col_data[64];
   int rounds = 0;
   unsigned char frame_buf[65536];
   size_t frame_len = 0;

   *lag_bytes = -1;

   buf = calloc(1, msglen);
   if (!buf)
   {
      goto error;
   }

   pgagroal_write_byte(buf, 'Q');
   pgagroal_write_int32(buf + 1, (int32_t)(4 + qlen));
   pgagroal_write_string(buf + 5, (char*)query);

   memset(&qmsg, 0, sizeof(struct message));
   qmsg.kind = 'Q';
   qmsg.length = (ssize_t)msglen;
   qmsg.data = buf;

   status = pgagroal_write_message(ssl, socket, &qmsg);
   if (status != MESSAGE_STATUS_OK)
   {
      goto error;
   }

   while (rounds++ < 16)
   {
      size_t offset = 0;

      status = pgagroal_read_block_message(ssl, socket, &tmsg);
      if (status != MESSAGE_STATUS_OK)
      {
         goto error;
      }

      if (frame_len + (size_t)tmsg->length > sizeof(frame_buf))
      {
         goto error;
      }

      memcpy(frame_buf + frame_len, tmsg->data, (size_t)tmsg->length);
      frame_len += (size_t)tmsg->length;

      while (frame_len - offset >= 5)
      {
         char msg_type = (char)frame_buf[offset];
         int32_t msg_len = pgagroal_read_int32((char*)frame_buf + offset + 1);
         size_t msg_size = (size_t)msg_len + 1;

         if (msg_len <= 0)
         {
            goto error;
         }

         if (frame_len - offset < msg_size)
         {
            break;
         }

         if (msg_type == 'D')
         {
            int16_t ncols = pgagroal_read_int16((char*)frame_buf + offset + 5);
            if (ncols >= 1)
            {
               size_t col_pos = offset + 7;
               int32_t col_len = pgagroal_read_int32((char*)frame_buf + col_pos);

               if (col_len == -1)
               {
                  *lag_bytes = -1;
                  got_value = true;
               }
               else if (col_len > 0 && col_len < (int32_t)sizeof(col_data) &&
                        col_pos + 4 + (size_t)col_len <= offset + msg_size)
               {
                  memset(col_data, 0, sizeof(col_data));
                  memcpy(col_data, frame_buf + col_pos + 4, (size_t)col_len);
                  *lag_bytes = (int64_t)strtoll(col_data, NULL, 10);
                  got_value = true;
               }
            }
         }
         else if (msg_type == 'E')
         {
            goto error;
         }
         else if (msg_type == 'Z')
         {
            if (got_value)
            {
               pgagroal_clear_message(tmsg);
               free(buf);
               return 0;
            }
         }

         offset += msg_size;
      }

      if (offset > 0)
      {
         memmove(frame_buf, frame_buf + offset, frame_len - offset);
         frame_len -= offset;
      }

      pgagroal_clear_message(tmsg);
      tmsg = NULL;
   }

   goto error;

error:
   free(buf);
   pgagroal_clear_message(tmsg);
   return 1;
}

int
pgagroal_server_get_connectivity_info(int server, char** status, char** primary, int64_t* behind_bytes)
{
   int fd = -1;
   int primary_server = -1;
   SSL* ssl = NULL;
   bool in_recovery = false;
   bool primary_known = false;
   bool is_primary = false;
   struct main_configuration* config = (struct main_configuration*)shmem;

   *status = "Down";
   *primary = "Unknown";
   *behind_bytes = -1;

   if (server < 0 || server >= config->number_of_servers)
   {
      return 1;
   }

   if (config->servers[server].host[0] == '/')
   {
      char pgsql[MISC_LENGTH];
      memset(pgsql, 0, sizeof(pgsql));
      snprintf(pgsql, sizeof(pgsql), ".s.PGSQL.%d", config->servers[server].port);
      if (pgagroal_connect_unix_socket(config->servers[server].host, pgsql, &fd))
      {
         goto done;
      }
   }
   else
   {
      if (pgagroal_connect(config->servers[server].host, config->servers[server].port, &fd,
                           config->keep_alive, config->nodelay))
      {
         goto done;
      }
   }

   *status = "Running";
   if (authenticate_direct_server(server, ssl, fd))
   {
      pgagroal_log_debug("connectivity_info: direct auth failed for server=%s", config->servers[server].name);
      goto fallback;
   }

   if (!pgagroal_get_primary(&primary_server) && primary_server >= 0)
   {
      is_primary = (server == primary_server);
      primary_known = true;
      *primary = is_primary ? "Yes" : "No";
   }

   if (check_recovery_status(ssl, fd, &in_recovery))
   {
      pgagroal_log_debug("connectivity_info: recovery query failed for server=%s", config->servers[server].name);
   }
   else
   {
      is_primary = !in_recovery;
      primary_known = true;
      *primary = is_primary ? "Yes" : "No";
   }

   /* For standbys, get replication lag bytes*/
   if (!primary_known || !is_primary)
   {
      if (get_replication_lag(ssl, fd, behind_bytes))
      {
         pgagroal_log_debug("connectivity_info: lag query failed for server=%s", config->servers[server].name);
      }
      else
      {
         pgagroal_log_trace("connectivity_info: lag=%ld for server=%s", *behind_bytes, config->servers[server].name);
      }
   }
   goto done;

fallback:
   if (!pgagroal_get_primary(&primary_server) && primary_server >= 0)
   {
      *primary = (server == primary_server) ? "Yes" : "No";
   }

done:
   if (fd >= 0)
   {
      pgagroal_disconnect(fd);
   }
   return 0;
}

int
pgagroal_get_primary(int* server)
{
   int primary;
   signed char server_state;
   struct main_configuration* config;

   primary = -1;
   config = (struct main_configuration*)shmem;

   /* Find PRIMARY */
   for (int i = 0; primary == -1 && i < config->number_of_servers; i++)
   {
      server_state = atomic_load(&config->servers[i].state);
      if (server_state == SERVER_PRIMARY)
      {
         pgagroal_log_trace("pgagroal_get_primary: server (%d) name (%s) primary", i, config->servers[i].name);
         primary = i;
      }
   }

   /* Find NOTINIT_PRIMARY */
   for (int i = 0; primary == -1 && i < config->number_of_servers; i++)
   {
      server_state = atomic_load(&config->servers[i].state);
      if (server_state == SERVER_NOTINIT_PRIMARY)
      {
         pgagroal_log_trace("pgagroal_get_primary: server (%d) name (%s) noninit_primary", i, config->servers[i].name);
         primary = i;
      }
   }

   /* Find the first valid server */
   for (int i = 0; primary == -1 && i < config->number_of_servers; i++)
   {
      server_state = atomic_load(&config->servers[i].state);
      if (server_state != SERVER_FAILOVER && server_state != SERVER_FAILED)
      {
         pgagroal_log_trace("pgagroal_get_primary: server (%d) name (%s) any (%d)", i, config->servers[i].name, server_state);
         primary = i;
      }
   }

   if (primary == -1)
   {
      goto error;
   }

   *server = primary;

   return 0;

error:

   *server = -1;

   return 1;
}

int
pgagroal_update_server_state(int slot, int socket, SSL* ssl)
{
   int status;
   int server;
   size_t size = 40;
   signed char state;
   char is_recovery[size];
   struct message qmsg;
   struct message* tmsg = NULL;
   struct deque* server_parameters = NULL;
   struct main_configuration* config;

   config = (struct main_configuration*)shmem;
   server = config->connections[slot].server;

   memset(&qmsg, 0, sizeof(struct message));
   memset(&is_recovery, 0, size);

   pgagroal_write_byte(&is_recovery, 'Q');
   pgagroal_write_int32(&(is_recovery[1]), size - 1);
   pgagroal_write_string(&(is_recovery[5]), "SELECT * FROM pg_is_in_recovery();");

   qmsg.kind = 'Q';
   qmsg.length = size;
   qmsg.data = &is_recovery;

   status = pgagroal_write_message(ssl, socket, &qmsg);
   if (status != MESSAGE_STATUS_OK)
   {
      goto error;
   }

   status = pgagroal_read_block_message(ssl, socket, &tmsg);
   if (status != MESSAGE_STATUS_OK)
   {
      goto error;
   }

   /* Read directly from the D message fragment */
   state = pgagroal_read_byte(tmsg->data + 54);

   pgagroal_clear_message(tmsg);

   if (state == 'f')
   {
      atomic_store(&config->servers[server].state, SERVER_PRIMARY);
   }
   else
   {
      atomic_store(&config->servers[server].state, SERVER_REPLICA);
   }

   if (pgagroal_extract_server_parameters(slot, &server_parameters))
   {
      pgagroal_log_trace("Unable to extract server_parameters for %s", config->servers[server].name);
      goto error;
   }

   if (process_server_parameters(server, server_parameters))
   {
      pgagroal_log_trace("uanble to process server_parameters for %s", config->servers[server].name);
      goto error;
   }

   pgagroal_deque_destroy(server_parameters);
   pgagroal_clear_message(tmsg);

   return 0;

error:
   pgagroal_log_trace("pgagroal_update_server_state: slot (%d) status (%d)", slot, status);

   pgagroal_deque_destroy(server_parameters);
   pgagroal_clear_message(tmsg);

   return 1;
}

int
pgagroal_server_status(void)
{
   struct main_configuration* config;

   config = (struct main_configuration*)shmem;

   for (int i = 0; i < NUMBER_OF_SERVERS; i++)
   {
      if (strlen(config->servers[i].name) > 0)
      {
         pgagroal_log_debug("pgagroal_server_status:    #: %d", i);
         pgagroal_log_debug("                        Name: %s", config->servers[i].name);
         pgagroal_log_debug("                        Host: %s", config->servers[i].host);
         pgagroal_log_debug("                        Port: %d", config->servers[i].port);
         switch (atomic_load(&config->servers[i].state))
         {
            case SERVER_NOTINIT:
               pgagroal_log_debug("                        State: NOTINIT");
               break;
            case SERVER_NOTINIT_PRIMARY:
               pgagroal_log_debug("                        State: NOTINIT_PRIMARY");
               break;
            case SERVER_PRIMARY:
               pgagroal_log_debug("                        State: PRIMARY");
               break;
            case SERVER_REPLICA:
               pgagroal_log_debug("                        State: REPLICA");
               break;
            case SERVER_FAILOVER:
               pgagroal_log_debug("                        State: FAILOVER");
               break;
            case SERVER_FAILED:
               pgagroal_log_debug("                        State: FAILED");
               break;
            default:
               pgagroal_log_debug("                        State: %d", atomic_load(&config->servers[i].state));
               break;
         }
      }
   }

   return 0;
}

int
pgagroal_server_failover(int slot)
{
   signed char primary;
   signed char old_primary;
   int ret = 1;
   struct main_configuration* config = NULL;

   config = (struct main_configuration*)shmem;

   primary = SERVER_PRIMARY;

   old_primary = config->connections[slot].server;

   if (atomic_compare_exchange_strong(&config->servers[old_primary].state, &primary, SERVER_FAILOVER))
   {
      ret = failover(old_primary);

      if (!fork())
      {
         pgagroal_flush_server(old_primary);
      }
   }

   return ret;
}

int
pgagroal_server_force_failover(int server)
{
   signed char cur_state;
   signed char prev_state;
   struct main_configuration* config = NULL;

   config = (struct main_configuration*)shmem;

   cur_state = atomic_load(&config->servers[server].state);

   if (cur_state != SERVER_FAILOVER && cur_state != SERVER_FAILED)
   {
      prev_state = atomic_exchange(&config->servers[server].state, SERVER_FAILOVER);

      if (prev_state == SERVER_NOTINIT || prev_state == SERVER_NOTINIT_PRIMARY || prev_state == SERVER_PRIMARY || prev_state == SERVER_REPLICA)
      {
         return failover(server);
      }
      else if (prev_state == SERVER_FAILED)
      {
         atomic_store(&config->servers[server].state, SERVER_FAILED);
      }
   }

   return 1;
}

int
pgagroal_server_clear(char* server)
{
   signed char state;
   struct main_configuration* config = NULL;

   config = (struct main_configuration*)shmem;

   for (int i = 0; i < config->number_of_servers; i++)
   {
      if (!strcmp(config->servers[i].name, server))
      {
         state = atomic_load(&config->servers[i].state);

         if (state == SERVER_FAILED)
         {
            atomic_store(&config->servers[i].state, SERVER_NOTINIT);
         }

         return 0;
      }
   }

   return 1;
}

int
pgagroal_server_switch(char* server)
{
   int old_primary = -1;
   int new_primary = -1;
   signed char state;
   struct main_configuration* config = NULL;

   config = (struct main_configuration*)shmem;

   pgagroal_log_debug("pgagroal: Attempting to switch to server '%s'", server);

   // Find current primary server
   for (int i = 0; i < config->number_of_servers; i++)
   {
      state = atomic_load(&config->servers[i].state);
      if (state == SERVER_PRIMARY)
      {
         old_primary = i;
         break;
      }
   }
   // Find target server by name
   for (int i = 0; i < config->number_of_servers; i++)
   {
      if (!strcmp(config->servers[i].name, server))
      {
         new_primary = i;
         break;
      }
   }

   if (old_primary != -1 && new_primary != -1)
   {
      if (old_primary == new_primary)
      {
         pgagroal_log_info("pgagroal: Server '%s' is already the primary - no switch needed", server);
         return 0;
      }
      else
      {
         pgagroal_log_info("pgagroal: Switching primary from '%s' to '%s'",
                           config->servers[old_primary].name,
                           config->servers[new_primary].name);
         atomic_store(&config->servers[old_primary].state, SERVER_FAILED);
         atomic_store(&config->servers[new_primary].state, SERVER_PRIMARY);
         return 0;
      }
   }
   else if (old_primary == -1 && new_primary != -1)
   {
      pgagroal_log_info("pgagroal: Setting '%s' as primary server (no previous primary found)",
                        config->servers[new_primary].name);
      atomic_store(&config->servers[new_primary].state, SERVER_PRIMARY);
      return 0;
   }
   else if (old_primary != -1 && new_primary == -1)
   {
      pgagroal_log_warn("pgagroal: Switch to server '%s' failed: server not found in configuration (current primary: '%s')",
                        server, config->servers[old_primary].name);
      return 1;
   }
   else
   {
      pgagroal_log_warn("pgagroal: Switch to server '%s' failed: no current primary server found and target server not found in configuration", server);
      return 1;
   }
}

static void
notify_standbys(int old_primary, int new_primary)
{
   pid_t pid;
   int status;
   struct main_configuration* config = (struct main_configuration*)shmem;

   pid = fork();
   if (pid == -1)
   {
      pgagroal_log_error("Notify: Unable to fork notify script");
      return;
   }
   else if (pid > 0)
   {
      waitpid(pid, &status, 0);

      if (WIFEXITED(status) && WEXITSTATUS(status) == 0)
      {
         pgagroal_log_info("Notify: Standbys notified successfully");
      }
      else
      {
         pgagroal_log_error("Notify: Error from notify script");
      }
   }
   else
   {
      int max_args = 5 + (config->number_of_servers * 2) + 1;
      char** args = malloc(max_args * sizeof(char*));

      if (!args)
      {
         pgagroal_log_error("Notify: Out of memory");
         exit(1);
      }

      int idx = 0;
      bool has_standbys = false;

      args[idx++] = "pgagroal_failover_notify_standbys";

      char* old_port = malloc(6);
      snprintf(old_port, 6, "%d", config->servers[old_primary].port);
      args[idx++] = config->servers[old_primary].host;
      args[idx++] = old_port;

      char* new_port = malloc(6);
      snprintf(new_port, 6, "%d", config->servers[new_primary].port);
      args[idx++] = config->servers[new_primary].host;
      args[idx++] = new_port;

      for (int i = 0; i < config->number_of_servers; i++)
      {
         if (i == old_primary || i == new_primary)
            continue;

         signed char state = atomic_load(&config->servers[i].state);
         if (state == SERVER_REPLICA || state == SERVER_NOTINIT || state == SERVER_NOTINIT_PRIMARY)
         {
            has_standbys = true;

            char* port = malloc(6);
            snprintf(port, 6, "%d", config->servers[i].port);
            args[idx++] = config->servers[i].host;
            args[idx++] = port;
         }
      }

      args[idx] = NULL;

      if (!has_standbys)
      {
         pgagroal_log_warn("Notify: No standbys to notify");
         exit(0);
      }

      execv(config->failover_notify_script, args);

      pgagroal_log_error("Notify: execv() failed");
      exit(1);
   }
}

static int
failover(int old_primary)
{
   signed char state;
   char old_primary_port[6];
   int new_primary;
   char new_primary_port[6];
   int status;
   pid_t pid;
   struct main_configuration* config = NULL;

   config = (struct main_configuration*)shmem;

   new_primary = -1;

   for (int i = 0; new_primary == -1 && i < config->number_of_servers; i++)
   {
      state = atomic_load(&config->servers[i].state);
      if (state == SERVER_NOTINIT || state == SERVER_NOTINIT_PRIMARY || state == SERVER_REPLICA)
      {
         new_primary = i;
      }
   }

   if (new_primary == -1)
   {
      pgagroal_log_error("Failover: New primary could not be found");
      atomic_store(&config->servers[old_primary].state, SERVER_FAILED);
      goto error;
   }

   pid = fork();
   if (pid == -1)
   {
      pgagroal_log_error("Failover: Unable to execute failover script");
      atomic_store(&config->servers[old_primary].state, SERVER_FAILED);
      goto error;
   }
   else if (pid > 0)
   {
      waitpid(pid, &status, 0);

      if (WIFEXITED(status) && WEXITSTATUS(status) == 0)
      {
         pgagroal_log_info("Failover: New primary is %s (%s:%d)", config->servers[new_primary].name, config->servers[new_primary].host, config->servers[new_primary].port);
         atomic_store(&config->servers[old_primary].state, SERVER_FAILED);
         atomic_store(&config->servers[new_primary].state, SERVER_PRIMARY);

         if (config->failover_notify_script[0] != '\0')
         {
            notify_standbys(old_primary, new_primary);
         }
      }
      else
      {
         if (WIFEXITED(status))
         {
            pgagroal_log_error("Failover: Error from failover script (exit %d)", WEXITSTATUS(status));
         }
         else
         {
            pgagroal_log_error("Failover: Error from failover script (status %d)", status);
         }

         atomic_store(&config->servers[old_primary].state, SERVER_FAILED);
         atomic_store(&config->servers[new_primary].state, SERVER_FAILED);
      }
   }
   else
   {
      memset(&old_primary_port, 0, sizeof(old_primary_port));
      memset(&new_primary_port, 0, sizeof(new_primary_port));

      sprintf(&old_primary_port[0], "%d", config->servers[old_primary].port);
      sprintf(&new_primary_port[0], "%d", config->servers[new_primary].port);

      execl(config->failover_script, "pgagroal_failover",
            config->servers[old_primary].host, old_primary_port,
            config->servers[new_primary].host, new_primary_port,
            (char*)NULL);
   }

   return 0;

error:

   return 1;
}

static int
process_server_parameters(int server, struct deque* server_parameters)
{
   int status = 0;
   int major = 0;
   int minor = 0;
   struct deque_iterator* iter = NULL;
   struct main_configuration* config;

   config = (struct main_configuration*)shmem;

   config->servers[server].version = 0;
   config->servers[server].minor_version = 0;

   pgagroal_deque_iterator_create(server_parameters, &iter);
   while (pgagroal_deque_iterator_next(iter))
   {
      pgagroal_log_trace("%s/process server_parameter '%s'", config->servers[server].name, iter->tag);
      char* value = pgagroal_value_to_string(iter->value, FORMAT_TEXT, NULL, 0);
      free(value);
      if (!strcmp("server_version", iter->tag))
      {
         char* server_version = pgagroal_value_to_string(iter->value, FORMAT_TEXT, NULL, 0);
         if (sscanf(server_version, "%d.%d", &major, &minor) == 2)
         {
            config->servers[server].version = major;
            config->servers[server].minor_version = minor;
         }
         else
         {
            pgagroal_log_error("Unable to parse server_version '%s' for %s",
                               server_version, config->servers[server].name);
            status = 1;
         }
         free(server_version);
         pgagroal_log_trace("%s/processed version: %d", config->servers[server].name, config->servers[server].version);
         pgagroal_log_trace("%s/processed minor_version: %d", config->servers[server].name, config->servers[server].minor_version);
      }
   }

   pgagroal_deque_iterator_destroy(iter);
   return status;
}
