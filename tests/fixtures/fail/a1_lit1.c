/* FAIL: a non-null integer literal is not null; free((int*)1) is UB. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    int *p = (int *)1;
    free(p);
    return 0;
}
