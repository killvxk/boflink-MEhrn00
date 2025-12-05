// module2.c - Second module with static global variable (same name!)

// Static global variable with same name
static int counter = 200;

// Export pointer to make symbol directly referenced
static int* get_counter(void) {
    return &counter;
}

// Exported function that uses the static variable
void process_module2(void) {
    int *p = get_counter();
    *p++;
}
