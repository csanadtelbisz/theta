// trylock on a held mutex fails, also after the OC checker lowers mutexes to flags.
#include <pthread.h>
#include <errno.h>
extern void abort(void);
void reach_error() { abort(); }
pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
int main() {
  pthread_mutex_lock(&m);
  if (pthread_mutex_trylock(&m) != EBUSY) reach_error(); /* held: must return EBUSY */
  return 0;
}
