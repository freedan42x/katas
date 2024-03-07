#include <stddef.h>
#include <stdlib.h>

typedef struct TreeNode {
	struct TreeNode *left, *right;
	int value;
} TreeNode;

TreeNode *tree(int value)
{
  TreeNode *t = malloc(sizeof(TreeNode));
  t->left = NULL;
  t->right = NULL;
  t->value = value;
  return t;
}

TreeNode *helper(size_t length, const int array[length], size_t ix)
{
  TreeNode *t = tree(array[ix-1]);
  if (ix*2-1 < length) t->left = helper(length, array, ix*2);
  if (ix*2 < length) t->right = helper(length, array, ix*2+1);
  return t;
}

TreeNode *array_to_tree(size_t length, const int array[length])
{
  if (length == 0) return NULL;
	return helper(length, array, 1);
}
