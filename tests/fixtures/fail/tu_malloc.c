void *calloc(unsigned long n, unsigned long m);
void free(void *p);
void *malloc(unsigned long n) { return (void *)n; }
int main(void) {
    long a = (long)calloc(1, 4);
    int *p = malloc(a);
    int *q = malloc(a);
    free(p);
    free(q);
    return 0;
}
