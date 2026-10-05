/* FAIL: a prototype-only callee cannot be assumed safe. */
void *malloc(unsigned long n);
void free(void *p);
void mystery(void *p);

int main(void) {
    void *p = malloc(8);
    mystery(p);
    free(p);
    return 0;
}
