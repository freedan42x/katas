#include <stdbool.h>

struct Node {
	struct Node *next;
	int data;
};

typedef bool (*predicate_func) (int);

int count_if (const struct Node *list, predicate_func predicate)
{
	return list ? predicate(list->data) + count_if(list->next, predicate) : 0;
}
