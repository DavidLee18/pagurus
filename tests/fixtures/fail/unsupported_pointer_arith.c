/* FAIL: pointer arithmetic is not modelled. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    void *p = malloc(8);
    p = p + 1;
    free(p);
    return 0;
}
