////////////////////////////////////////////////////////
// shape.h
typedef struct _shape_vtable_t {
  double (*get_area)();
  double (*get_perimenter)();
  void (*destroy)();
} shape_vtable_t;

typedef struct _shape_t {
  shape_vtable_t *vtable;
} shape_t;

unsigned int shape_get_area(const void *shape);
unsigned int shape_get_perimeter(const void *shape);
void shape_destroy(const void *shape);

////////////////////////////////////////////////////////
// right_triangle.h

typedef struct _right_triangle_t {
  shape_t shape;
  double side1;
  double side2;
} right_triangle_t;

right_triangle_t *right_triangle_create(double side1, double side2);

////////////////////////////////////////////////////////
// right_triangle.c

#include <math.h>
#include <stdlib.h>

static double get_area(const right_triangle_t *right_triangle) {
  return right_triangle->side1 * right_triangle->side2 / 2;
}

static double get_perimeter(const right_triangle_t *right_triangle) {
  double a = right_triangle->side1;
  double b = right_triangle->side2;
  return a + b + sqrt(a * a + b * b);
}

static void destroy(const right_triangle_t *right_triangle) {
  free(right_triangle);
}

static shape_vtable_t right_triangle_vtable = {
  get_area,
  get_perimeter,
  destroy
};

right_triangle_t *right_triangle_create(double side1, double side2) {
  right_triangle_t *right_triangle = malloc(sizeof(right_triangle_t));
  right_triangle->shape.vtable = &right_triangle_vtable;
  right_triangle->side1 = side1;
  right_triangle->side2 = side2;
  return right_triangle;
}
