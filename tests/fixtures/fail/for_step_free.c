/* FAIL: a for-step that frees, then a later free of the same pointer. */
void *malloc(unsigned long n);
void free(void *p);
int main(void) {
    int *p = malloc(4);
    int i;
    for (i = 0; i < 1; free(p)) {
        p = malloc(4);
        i = 1;
    }
    free(p);
    return 0;
}
