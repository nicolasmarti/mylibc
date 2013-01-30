#ifndef BITMAP_H
#define BITMAP_H

#include <stddef.h>
#include <stdlib.h>
#include <string.h>

// returns (x^y)
size_t size_pow(size_t x, size_t y);

// returns (2^x)
size_t size_pow2(size_t x);

//returns cell(log(x)/log(2^y)) -> (2^y)^(\result - 1) <= x <= (2^y)^(\result)
size_t size_cell_log_pow2(size_t x, size_t y);

// same but for floor
size_t size_floor_log_pow2(size_t x, size_t y);

// the test
void size_cell_log_pow2_test(size_t x, size_t y);

// definition of a bitmap
// the storage is considered to be right after the structure in memory
typedef struct {
  size_t nb_levels;
  size_t nb_elements;
} bitmap_t;

// the data structure which identify a bit in the map
typedef struct _bit_id{
  bitmap_t* bm; // the bitmap
  size_t level; // the level in the tree
  size_t offset; // the offset of the bulk in the level
  size_t index; // the index of the bit in the bulk
} bit_id_t;

// this function takes a bit_id_t and mutate it into its father
// returns 0 if faled and 1 if succeed
size_t parent(bit_id_t* bit);

// this function takes a bit_id_t and mutate it into its child (index will be 0 by default)
// returns 0 if faled and 1 if succeed
size_t child(bit_id_t* bit);

// basic set/reset of a bit
void set(bit_id_t* bit);
void reset(bit_id_t* bit);

//make a bit_id from an index
// returns 1 if succeeded, 0 if failed
size_t get_bit_id(bitmap_t* bm, size_t index, bit_id_t* bit);

// set/reset with & or | propagation
void set_bit_orb(bit_id_t bit);
void reset_bit_orb(bit_id_t bit);

size_t set_orb(bitmap_t* bm, size_t index);
size_t reset_orb(bitmap_t* bm, size_t index);

// for andb bitmap (done but not used, so signature are commented)
//void set_bit_andb(bit_id_t bit);
//void reset_bit_andb(bit_id_t bit);

// create a bitmap;
bitmap_t* create_bitmap(size_t nb_elements);

// create an 'iterator'
void create_iterator(bitmap_t* bm, bit_id_t* bit);

// find set index
// this works only in a orb bitmap
size_t find_set(bit_id_t* bit);
// this version just add 1 to the index and call above function
size_t find_next_set(bit_id_t* bit);


#endif
