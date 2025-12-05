// go.c - Entry point for the BOF

// External declarations
extern void process_module1(void);
extern void process_module2(void);

// BOF entry point
void go(void) {
    // Call both modules - each has its own 'helper' function
    // After deduplication, they will have unique names
    process_module1();
    process_module2();
}
