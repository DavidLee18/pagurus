/* FAIL: ff consumes the first argument; the second is a borrow of the same
   pointer after it was moved — use-after-move. */
void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void ff(void*a,void*b){free(a);}
int main(void){int*p=malloc(4);ff(p,p);return 0;}
