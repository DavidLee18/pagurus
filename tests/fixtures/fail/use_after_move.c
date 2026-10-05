/* FAIL: pointer assignment moves unique ownership. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    void *p = malloc(8);
    void *q = p;
    free(p);
    free(q);
    return 0;
}
