typedef int (*reduce_func) (int accumulator, int value);

struct Node {
	struct Node *next;
	int data;
};

int reduce_list (const struct Node *list, reduce_func f, int init_val)
{
  if (!list) return init_val;
  return f(reduce_list(list->next, f, init_val), list->data);
}
