/* FAIL: only the else branch returns; the then branch frees, then the
   continuation frees again — a real double free when c is true. */
void *malloc(unsigned long n);
void free(void *p);
int main(void) {
    int *p = malloc(4);
    int c = 1;
    if (c) {
        free(p);
    } else {
        return 0;
    }
    free(p);
    return 0;
}
