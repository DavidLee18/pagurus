/* FAIL: realloc consumes p; freeing p afterwards is use-after-move / double-free. */
void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
int main(void){int*p=malloc(4);int*q=realloc(p,8);free(p);free(q);return 0;}
