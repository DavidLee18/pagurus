/* PASS: statements after return do not run, so the second free is dead. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    int *p = malloc(4);
    free(p);
    return 0;
    free(p);
}
