struct List {
	struct List *next;
	int data;
};

int last_index_of (const struct List *list, int search_val)
{
  int ix = -1;
  
  for (int i = 0; list; i++) {
    if (list->data == search_val) ix = i;
    list = list->next;
  }
	
  return ix;
}
