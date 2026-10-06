void *malloc(unsigned long n);
void *calloc(unsigned long n, unsigned long m);
void free(void *p);
int consume(int *p, int r) { free(p); return r; }
void use(int *p) { if (p) { } }
int main(void) { int *p = malloc(4); int i = 0; do { use(p); i = i + 1; } while (i < 3); free(p); return 0; }
