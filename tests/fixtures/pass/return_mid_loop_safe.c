/* PASS: return in the loop body ends that path; the post-loop free sees the 0-iteration env. */
void *malloc(unsigned long n);
void *calloc(unsigned long n, unsigned long m);
void free(void *p);
int consume(int *p, int r) { free(p); return r; }
void use(int *p) { if (p) { } }
int main(void) { int *p = malloc(4); int i = 0; while (i < 10) { free(p); return 0; } free(p); return 0; }
