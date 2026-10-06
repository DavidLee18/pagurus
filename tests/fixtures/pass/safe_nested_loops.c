void *malloc(unsigned long n);
void *calloc(unsigned long n, unsigned long m);
void free(void *p);
int consume(int *p, int r) { free(p); return r; }
void use(int *p) { if (p) { } }
int main(void) { int *p = malloc(4); int i = 0; int j; while (i < 2) { j = 0; while (j < 2) { use(p); j = j + 1; } i = i + 1; } free(p); return 0; }
