void *malloc(unsigned long n);
void *calloc(unsigned long n, unsigned long m);
void free(void *p);
int consume(int *p, int r) { free(p); return r; }
void use(int *p) { if (p) { } }
int main(void) { int i; int *p = malloc(4); for (i = 0; i < 1; i++) { for (; consume(p, 0);) { p = malloc(4); } p = malloc(4); } free(p); free(p); return 0; }
