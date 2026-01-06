#include <stddef.h>

/*@ requires \valid(ptr); */ 
/*@ ensures *ptr == value; */ 
void set_value(int *ptr, int value) {
    /*@ assert ptr != NULL; */ 
    *ptr = value;
}

/*@ requires \valid(ptr); */ 
/*@ ensures *ptr == value; */ 
int get_value(int *ptr) {
    /*@ assert ptr != NULL; */ 
    return *ptr;
}

int main() {
    int x = 0;
    set_value(&x, 42);
    int value = get_value(&x);
    return 0;
}
