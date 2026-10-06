/* FAIL: assigning 7 to a pointer is not known-null; a later free is UB. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    int *p = malloc(4);
    free(p);
    p = 7;
    free(p);
    return 0;
}
