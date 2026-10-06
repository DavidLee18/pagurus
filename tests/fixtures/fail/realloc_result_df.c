/* FAIL: realloc result is a unique owner; freeing it twice is a double free. */
void *malloc(unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
int main(void){int*p=malloc(4);p=realloc(p,8);free(p);free(p);return 0;}
