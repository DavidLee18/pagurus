/* Clean: unique owner is allocated and then dropped exactly once. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    void *p = malloc(8);
    free(p);
    return 0;
}
