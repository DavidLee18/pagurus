void *malloc(unsigned long n);
void *calloc(unsigned long n, unsigned long m);
void free(void *p);
int consume(int *p, int r) { free(p); return r; }
void use(int *p) { if (p) { } }
int main(void) { int i = 0; int *p = malloc(4); while (i < 1) { while (consume(p, 0)) { p = malloc(4); } i = 1; } free(p); return 0; }
