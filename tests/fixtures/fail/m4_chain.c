/* FAIL: a->b->free is Always-consume through the chain. */
void *malloc(unsigned long n);
void free(void *p);

void b(int *q) { free(q); }
void a(int *p) { b(p); }

int main(void) {
    int *p = malloc(4);
    a(p);
    free(p);
    return 0;
}
