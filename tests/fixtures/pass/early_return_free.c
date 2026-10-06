/* PASS: a returning branch that frees must not join into the continuation. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    int *p = malloc(4);
    int err = 1;
    if (err) {
        free(p);
        return -1;
    }
    free(p);
    return 0;
}
