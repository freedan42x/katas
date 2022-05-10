struct Node {
	struct Node *next;
	int data;
};

int index_of(const struct Node *list, int search_val)
{
  int ix = 0;
  while (list) {
    if (list->data == search_val) return ix;
    ix += 1;
    list = list->next;
  }
  return -1;
}
