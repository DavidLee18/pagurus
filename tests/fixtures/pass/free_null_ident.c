/* PASS: identifier NULL is modelled as the null pointer constant. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    void *p = malloc(4);
    free(NULL);
    free(p);
    return 0;
}
