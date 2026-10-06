/* FAIL: a realloc *defined* in this TU is not the synthetic allocator. */
void *malloc(unsigned long n);
void free(void *p);
void *realloc(void *p, unsigned long n) { return p; }
int main(void) {
    int *p = malloc(4);
    int *q = realloc(p, 8);
    free(p);
    free(q);
    return 0;
}
