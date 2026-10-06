void *malloc(unsigned long n);
void *calloc(unsigned long n, unsigned long m);
void free(void *p);
int consume(int *p, int r) { free(p); return r; }
void use(int *p) { if (p) { } }
int main(void) { int i = 0; int j = 0; int *p = malloc(4); while (consume(p, i < 1)) { while (j < 1) { p = malloc(4); j = 1; } i = 1; } free(p); return 0; }
