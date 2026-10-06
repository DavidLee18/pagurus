/* PASS: overwriting an owner with NULL, then free, is free(NULL). Leak is out of scope. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    void *p = malloc(4);
    p = NULL;
    free(p);
    return 0;
}
