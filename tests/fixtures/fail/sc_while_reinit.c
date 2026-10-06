void *malloc(unsigned long n);
void *calloc(unsigned long n, unsigned long m);
void free(void *p);
int consume(int *p, int r) { free(p); return r; }
void use(int *p) { if (p) { } }
int main(void) { int x = 0; int *p = malloc(4); free(p); while (x && (p = malloc(4))) { x = 0; } free(p); return 0; }
