void *malloc(unsigned long n);
void *calloc(unsigned long n, unsigned long m);
void free(void *p);
int consume(int *p, int r) { free(p); return r; }
void use(int *p) { if (p) { } }
int main(void) { int *p = malloc(4); int k = 0; while (p && k < 3) { use(p); k = k + 1; } free(p); return 0; }
