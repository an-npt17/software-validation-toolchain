// example.c - Sample code for formal verification
// This demonstrates various properties that can be verified

#include <stdbool.h>
#include <stddef.h>

// ============================================
// Example 1: Buffer Operations with ACSL
// ============================================

/*@
  requires \valid(buffer + (0..size-1));
  requires size > 0;
  ensures \forall integer i; 0 <= i < size ==> buffer[i] == 0;
  assigns buffer[0..size-1];
*/
void clear_buffer(char *buffer, size_t size) {
  /*@ loop invariant 0 <= i <= size;
      loop invariant \forall integer j; 0 <= j < i ==> buffer[j] == 0;
      loop assigns i, buffer[0..size-1];
      loop variant size - i;
  */
  for (size_t i = 0; i < size; i++) {
    buffer[i] = 0;
  }
}

// ============================================
// Example 2: Array Bounds Checking
// ============================================

/*@
  requires \valid(array + (0..size-1));
  requires 0 <= index < size;
  assigns array[index];
*/
void set_array_element(int *array, size_t size, size_t index, int value) {
  array[index] = value;
}

/*@
  requires \valid_read(array + (0..size-1));
  requires 0 <= index < size;
  ensures \result == array[index];
*/
int get_array_element(const int *array, size_t size, size_t index) {
  return array[index];
}

// ============================================
// Example 3: Pointer Null Checking
// ============================================

/*@
  requires ptr != \null;
  ensures \result == *ptr;
*/
int safe_dereference(int *ptr) { return *ptr; }

// ============================================
// Example 4: String Operations
// ============================================

/*@
  requires \valid(dest + (0..dest_size-1));
  requires \valid_read(src + (0..strlen(src)));
  requires dest_size > strlen(src);
  ensures strcmp(dest, src) == 0;
  assigns dest[0..dest_size-1];
*/
void safe_string_copy(char *dest, const char *src, size_t dest_size) {
  size_t i = 0;
  /*@ loop invariant 0 <= i <= dest_size;
      loop invariant \forall integer j; 0 <= j < i ==> dest[j] == src[j];
      loop assigns i, dest[0..dest_size-1];
      loop variant dest_size - i;
  */
  while (i < dest_size - 1 && src[i] != '\0') {
    dest[i] = src[i];
    i++;
  }
  dest[i] = '\0';
}

// ============================================
// Example 5: Integer Overflow Protection
// ============================================

/*@
  requires INT_MIN <= a <= INT_MAX;
  requires INT_MIN <= b <= INT_MAX;
  requires a + b <= INT_MAX;
  requires a + b >= INT_MIN;
  ensures \result == a + b;
*/
int safe_add(int a, int b) { return a + b; }

// ============================================
// Example 6: Division by Zero Protection
// ============================================

/*@
  requires divisor != 0;
  ensures \result == dividend / divisor;
*/
int safe_divide(int dividend, int divisor) { return dividend / divisor; }

// ============================================
// Example 7: Memory Allocation Verification
// ============================================

/*@
  requires count > 0;
  requires count * sizeof(int) <= SIZE_MAX;
  ensures \result == \null || \valid(\result + (0..count-1));
*/
int *allocate_array(size_t count) {
  // In real code, would use malloc
  // For verification, we just show the contract
  return (int *)0; // Placeholder
}

// ============================================
// Example 8: Conditional Logic
// ============================================

/*@
  requires \valid_read(array + (0..size-1));
  requires size > 0;
  ensures \result >= 0 ==> 0 <= \result < size;
  ensures \result >= 0 ==> array[\result] == target;
  ensures \result < 0 ==> (\forall integer i; 0 <= i < size ==> array[i] !=
  target);
*/
int find_element(const int *array, size_t size, int target) {
  /*@ loop invariant 0 <= i <= size;
      loop invariant \forall integer j; 0 <= j < i ==> array[j] != target;
      loop assigns i;
      loop variant size - i;
  */
  for (size_t i = 0; i < size; i++) {
    if (array[i] == target) {
      return (int)i;
    }
  }
  return -1;
}

// ============================================
// Example 9: Complex Pre/Post Conditions
// ============================================

/*@
  requires \valid(array + (0..size-1));
  requires size > 0;
  ensures \forall integer i; 0 <= i < size-1 ==> array[i] <= array[i+1];
  assigns array[0..size-1];
*/
void bubble_sort(int *array, size_t size) {
  // Simplified bubble sort for verification
  /*@ loop invariant 0 <= i <= size;
      loop assigns i, array[0..size-1];
      loop variant size - i;
  */
  for (size_t i = 0; i < size; i++) {
    /*@ loop invariant i < j <= size;
        loop assigns j, array[0..size-1];
        loop variant size - j;
    */
    for (size_t j = i + 1; j < size; j++) {
      if (array[i] > array[j]) {
        int temp = array[i];
        array[i] = array[j];
        array[j] = temp;
      }
    }
  }
}

// ============================================
// Example 10: Struct Operations
// ============================================

typedef struct {
  int *data;
  size_t size;
  size_t capacity;
} Vector;

/*@
  requires \valid(vec);
  requires vec->data == \null ==> vec->size == 0;
  requires vec->data != \null ==> \valid(vec->data + (0..vec->capacity-1));
  requires vec->size <= vec->capacity;
  requires index < vec->size;
  ensures \result == vec->data[index];
*/
int vector_get(const Vector *vec, size_t index) { return vec->data[index]; }

// ============================================
// Example 11: Without ACSL (for comparison)
// These will have violations detected by verification tools
// ============================================

// UNSAFE: No bounds checking
void unsafe_array_access(int *array, int index, int value) {
  array[index] = value; // CBMC will flag this
}

// UNSAFE: Possible null dereference
int unsafe_pointer_access(int *ptr) {
  return *ptr; // Frama-C will require proof this is valid
}

// UNSAFE: Possible overflow
int unsafe_multiply(int a, int b) {
  return a * b; // CBMC will check for overflow
}

// UNSAFE: Division by zero
int unsafe_division(int a, int b) {
  return a / b; // Will be flagged
}

// Main function for testing
int main(void) {
  char buffer[10];
  clear_buffer(buffer, 10);

  int array[5] = {1, 2, 3, 4, 5};
  int value = get_array_element(array, 5, 2);

  int sum = safe_add(10, 20);
  int quotient = safe_divide(100, 5);

  return 0;
}
