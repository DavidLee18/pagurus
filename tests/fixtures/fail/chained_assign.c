/* FAIL: chained assignment must move the unique owner, not duplicate it. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    void *p;
    void *q;
    q = p = malloc(8);
    free(p);
    free(q);
    return 0;
}
