// module1.c - First module with static global variable

// Static global variable
static int counter = 100;

// Export pointer to make symbol directly referenced
static int* get_counter(void) {
    return &counter;
}

// Exported function that uses the static variable  
void process_module1(void) {
    int *p = get_counter();
    *p++;
}
