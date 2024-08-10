#include <stdlib.h>

struct list_t {
  int value;
  struct list_t *tail;
};

struct queue_t {
  struct list_t *in, *out;
};

struct list_t *cons(int value, struct list_t *tail) {
  struct list_t *new_cell = (struct list_t *) malloc(sizeof(struct list_t));
  if(!new_cell) {
    exit(1);
  }

  new_cell->value = value;
  new_cell->tail = tail;

  return new_cell;
}

int uncons(struct list_t **list_ptr) {
  struct list_t *tail = (*list_ptr)->tail;
  int value = (*list_ptr)->value;

  free(*list_ptr);
  *list_ptr = tail;

  return value;
}

struct list_t *nreverse(struct list_t *list) {
  struct list_t *prev, *curr, *next;
  prev = NULL;
  curr = list;
  while(curr) {
    struct list_t *next = curr->tail;
    curr->tail = prev;
    prev = curr;
    curr = next;
  }

  return prev;
}

struct queue_t *new_queue() {
  struct queue_t *queue_ptr = (struct queue_t *) malloc(sizeof(struct queue_t));
  if(!queue_ptr) {
    exit(1);
  }

  queue_ptr->in = NULL;
  queue_ptr->out = NULL;

  return queue_ptr;
}

void push_back(struct queue_t *queue, int val) {
  queue->in = cons(val, queue->in);
}

void normalize(struct queue_t *queue) {
  if(!queue->out) {
    queue->out = nreverse(queue->in);
    queue->in = NULL;
  }
}

int pop_front(struct queue_t *queue) {
  normalize(queue);
  return uncons(&queue->out);
}
