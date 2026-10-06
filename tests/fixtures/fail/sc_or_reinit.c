void *malloc(unsigned long n);
void *calloc(unsigned long n, unsigned long m);
void free(void *p);
int consume(int *p, int r) { free(p); return r; }
void use(int *p) { if (p) { } }
int main(void) { int x = 1; int *p = malloc(4); free(p); if (x || (p = malloc(4))) { } free(p); return 0; }
