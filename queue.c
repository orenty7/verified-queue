#include <stdlib.h>

struct list_t {
  int value;
  struct list_t *tail;
};

struct queue {
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


void push_back(struct queue *queue, int val) {
  queue->in = cons(val, queue->in);
}

void normalize(struct queue *queue) {
  if(!queue->out) {
    queue->out = nreverse(queue->in);
    queue->in = NULL;
  }
}

int pop_front(struct queue *queue) {
  normalize(queue);
  return uncons(&queue->out);
}