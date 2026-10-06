void *malloc(unsigned long n);
void *calloc(unsigned long n, unsigned long m);
void free(void *p);
int consume(int *p, int r) { free(p); return r; }
void use(int *p) { if (p) { } }
int main(void) { char *p = malloc(4); char *q = malloc(4); long a = (long)p; long b = (long)q; q += a - b; free(p); free(q); return 0; }
