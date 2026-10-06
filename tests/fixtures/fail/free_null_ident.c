/* FAIL: the identifier NULL is not rewritten; free(NULL) is rejected. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    void *p = malloc(4);
    free(NULL);
    free(p);
    return 0;
}
