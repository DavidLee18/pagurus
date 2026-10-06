/* PASS: free(0) / free((void *)0) is a defined no-op. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    void *p = malloc(4);
    free(0);
    free((void *)0);
    free(p);
    return 0;
}
