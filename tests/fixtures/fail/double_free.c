/* FAIL: free consumes ownership; a second free is a double free. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    void *p = malloc(8);
    free(p);
    free(p);
    return 0;
}
