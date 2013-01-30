#include "bitmap.h"
#include <stdio.h>
#include <string.h>

char *byte_to_binary
(
 size_t x
)
{
    static char b[100];
    b[0] = '\0';

    size_t z;
    for (z = 1; z > 0; z <<= 1)
    {
        strcat(b, ((x & z) == z) ? "1" : "0");
    }

    return b;
}


size_t size_pow(size_t x, size_t y)
{
  size_t res = 1;

  //printf("\ninit: x = %lu, y = %lu, res = %lu\n", x, y, res);

  while (y)
    {
      res *= x;
      y--;
      //printf("loop body end: x = %lu, y = %lu, res = %lu\n", x, y, res);
    }

  //printf("result := %lu\n\n", res);

  return res;
}

size_t size_pow2(size_t x)
{
  return 1 << x;
}


size_t size_floor_log_pow2(size_t x, size_t y)
{

  size_t res = 0;

  //printf("\ninit: x = %lu, y = %lu, res = %lu\n", x, y, res);

  while (x >>= y)
    {
      res++;
      //printf("loop body end: x = %lu, y = %lu, res = %lu\n", x, y, res);
    }

  //printf("result := %lu\n\n", res);

  return res;

}

size_t size_cell_log_pow2(size_t x, size_t y)
{

  size_t res = 1;

  //printf("\ninit: x = %lu, y = %lu, res = %lu\n", x, y, res);

  while (x >>= y)
    {
      res++;
      //printf("loop body end: x = %lu, y = %lu, res = %lu\n", x, y, res);
    }

  //printf("result := %lu\n\n", res);

  return res;

}

void size_cell_log_pow2_test(size_t x, size_t y)
{
  size_t res; 
  size_t ub;
  size_t lb;

  //printf("size_cell_log_pow2(%lu, %lu) = ", x, y); fflush(stdout);
  res = size_cell_log_pow2(x, y);
  //printf("%lu\n", res); fflush(stdout);

  //printf("size_pow(size_pow2(%lu), %lu) = ", y, res); fflush(stdout);
  ub = size_pow(size_pow2(y), res);
  //printf("%lu\n", ub); fflush(stdout);

  //printf("size_pow(size_pow2(%lu), %lu) = ", y, res - 1); fflush(stdout);
  lb = size_pow(size_pow2(y), res - 1);
  //printf("%lu\n", ub); fflush(stdout);


  if (!(res > 0 && (lb <= x) && (x <= ub))){
    printf("\n------------------------------\n");
    printf("size_cell_log_pow2 misbehaved!!!\n");
    printf("size_cell_log_pow2(%lu, %lu) = %lu \n", x, y, res);

    printf("size_pow2(%lu) = %lu\n", y, size_pow2(y));
    printf("size_pow(%lu, %lu) = %lu\n", size_pow2(y), res, ub);    

    if (!(res > 0)){
      printf("assert 1 failed: ! (%lu > 0) !!\n", res);
    }

    if (!((lb <= x))){
      printf("assert 2 failed: ! (%lu <= %lu)  !!\n", lb, x);
    }

    if (!((x <= ub))){
      printf("assert 3 failed: ! (%lu <= %lu)  !!\n", x, ub);
    }
    printf("------------------------------\n\n"); fflush(stdout);
  }

  //printf("\n"); fflush(stdout);
}

size_t parent(bit_id_t* bit){

  // test if we are at the last level
  if (bit->level == 0)
    return 0;

  // updating
  --bit->level;
  bit->index = bit->offset % (sizeof(size_t) * 8);
  bit->offset /= (sizeof(size_t) * 8);
 
  return 1;
}

size_t child(bit_id_t* bit){

  // check if we are on the last level
  if (bit->level == bit->bm->nb_levels - 1)
    return 0;

  // updating
  ++bit->level;
  bit->offset = bit->offset * (sizeof(size_t) * 8) + bit->index;
  bit->index = 0;

  return 1;

}

void set(bit_id_t* bit){

  // TODO: find better in terms of bitshifting than that
  size_t* location = (size_t*)(bit->bm + 1) + size_pow(sizeof(size_t) * 8, bit->level) - 1 + bit->offset;

  *location &= (size_t)1 << bit->index;
  
}

void reset(bit_id_t* bit){

  size_t* location = (size_t*)(bit->bm + 1) + size_pow(sizeof(size_t) * 8, bit->level) - 1 + bit->offset;

  *location |= ~((size_t)1 << bit->index);

}

void set_bit_orb(bit_id_t bit){

  char propagate = 1;

  while (propagate){

    size_t* location = (size_t*)(bit.bm + 1) + size_pow(sizeof(size_t) * 8, bit.level) - 1 + bit.offset;

    //printf("set_bit_orb before({%p, %lu, %lu, %lu}) -> 0b%s\n", bit.bm, bit.level, bit.offset, bit.index, byte_to_binary(*location)); fflush(stdout);

    // propagate is set in two step to avoid a ifte
    propagate = !(*location);

    *location |= (size_t)1 << bit.index;

    //printf("set_bit_orb after({%p, %lu, %lu, %lu}) -> 0b%s\n", bit.bm, bit.level, bit.offset, bit.index, byte_to_binary(*location)); fflush(stdout);

    propagate = propagate && parent(&bit);

  }

}

void reset_bit_orb(bit_id_t bit){

  size_t* location;

  do {

    location = (size_t*)(bit.bm + 1) + size_pow(sizeof(size_t) * 8, bit.level) - 1 + bit.offset;

    *location &= ~((size_t)1 << bit.index);

  } while(!(*location) && parent(&bit));

}

void set_bit_andb(bit_id_t bit){

  size_t* location;

  do {

    location = (size_t*)(bit.bm + 1) + size_pow(sizeof(size_t) * 8, bit.level) - 1 + bit.offset;

    *location |= (size_t)1 << bit.index;

  } while(!(~(*location)) && parent(&bit));

}

void reset_bit_andb(bit_id_t bit){

  char propagate = 1;

  while (propagate){

    size_t* location = (size_t*)(bit.bm + 1) + size_pow(sizeof(size_t) * 8, bit.level) - 1 + bit.offset;

    // propagate is set in two step to avoid a ifte
    propagate = !(~(*location));

    *location &= ~((size_t)1 << bit.index);

    propagate = propagate && parent(&bit);

  }
  

}


size_t get_bit_id(bitmap_t* bm, size_t index, bit_id_t* bit){

  // check the index
  if (index >= bm->nb_elements)
    return 0;
  
  bit->bm = bm;
  bit->level = bm->nb_levels - 1;
  bit->offset = index / (sizeof(size_t) * 8);
  bit->index = index % (sizeof(size_t) * 8);

  return 1;
}


size_t set_orb(bitmap_t* bm, size_t index){

  bit_id_t bit;  

  if (!get_bit_id(bm, index, &bit))
    return 0;

  set_bit_orb(bit);

  return 1;

}


size_t reset_orb(bitmap_t* bm, size_t index){

  bit_id_t bit;  

  if (!get_bit_id(bm, index, &bit))
    return 0;

  reset_bit_orb(bit);

  return 1;

}


bitmap_t* create_bitmap(size_t nb_elements){


  size_t nb_levels = size_cell_log_pow2(nb_elements, size_floor_log_pow2(sizeof(size_t*) * 8, 1));

  size_t nb_bulks = size_pow(sizeof(size_t*) * 8, nb_levels);

  bitmap_t* result = (bitmap_t*)malloc(sizeof(bitmap_t) + sizeof(size_t) * nb_bulks);  

  memset(result, 0 , sizeof(bitmap_t) + sizeof(size_t) * nb_bulks);

  result->nb_levels = nb_levels;
  result->nb_elements = nb_elements;

  return result;

}

void create_iterator(bitmap_t* bm, bit_id_t* bit){

  memset(bit, 0, sizeof(bit_id_t));

  bit->bm = bm;
  

}


size_t bit_to_index(bit_id_t* bit){

  return bit->offset * sizeof(size_t) * 8 + bit->index;

}

// this works only in a orb bitmap
size_t find_next_set(bit_id_t* bit){

  bit->index++;
  return find_set(bit);

}

size_t find_set(bit_id_t* bit){

  size_t* location = (size_t*)(bit->bm + 1) + size_pow(sizeof(size_t) * 8, bit->level) - 1 + bit->offset;

  //printf("find_set({%p, %lu, %lu, %lu}) -> 0b%s\n", bit->bm, bit->level, bit->offset, bit->index, byte_to_binary(*location)); fflush(stdout);

  // look in the current bulk on the next indices until finding one set
  while (bit->index < sizeof(size_t*) * 8){
    // if we find a bit set, 
    if (*location & ((size_t)1 << bit->index))
      {
	// then we try to go down
	if (child(bit)){
	  
	  // tail recursion!
	  return find_set(bit);

	} else {
	  // we have found one!
	  return bit_to_index(bit);

	}
      }
    bit->index++;
  }
  
  // we did not found anything in this bulk: try go to the parent
  if (parent(bit)) {
    // increment the index
    bit->index++;
    // tail recursion!
    return find_set(bit);
  } else {
    // we failed
    return bit->bm->nb_elements;    
  } 

}
