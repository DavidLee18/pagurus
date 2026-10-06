void *malloc(unsigned long n);
void *calloc(unsigned long n, unsigned long m);
void free(void *p);
int consume(int *p, int r) { free(p); return r; }
void use(int *p) { if (p) { } }
int main(void) { int *p = malloc(4); int i; for (i = 0; consume(p, i < 1); i++) { p = malloc(4); continue; } free(p); return 0; }
