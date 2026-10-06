void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
int*dup(int*p){return p;}
int main(void){int*p=malloc(4);int*q=dup(p);free(p);free(q);return 0;}
