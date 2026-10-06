void *malloc(unsigned long n);
void *calloc(unsigned long n, unsigned long m);
void free(void *p);
int consume(int *p, int r) { free(p); return r; }
void use(int *p) { if (p) { } }
int main(void) { int *p = malloc(4); int i = 0; for (; i < 1;) { free(p); i = 1; p = malloc(4); free(p); } free(p); return 0; }
