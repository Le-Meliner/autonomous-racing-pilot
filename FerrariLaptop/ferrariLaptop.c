#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "ferrariLaptop.h"

char gmap[MAX_HEIGHT][MAX_WIDTH + 2];
int gwidth, gheight;

/**
 * @brief Compute the gas consumption of a requested acceleration
 *
 * CAUTION: Even an illegal move will result in gas consumption. Producing
 * illegal moves should be prevented as much as possible!
 *
 * @param accX Acceleration x component
 * @param accY Acceleration y component
 * @param speedX Speed x component
 * @param speedY Speed y component
 * @param inSand (boolean)
 * @return Number of gas units consumed
 */
int gasConsumption(int accX, int accY, int speedX, int speedY, int inSand)
{
  int gas = accX * accX + accY * accY;
  gas += (int)(sqrt(speedX * speedX + speedY * speedY) * 3.0 / 2.0);
  if (inSand) {
    gas += 1;
  }
  return -gas;
}

int main()
{
  int row;
  int myX, myY;
  int width, height;
  int gasLevel;
  int boosts = BOOSTS_AT_START;
  int round = 0;
  int accelerationX = 1, accelerationY = 0;
  int speedX = 0, speedY = 0;
  char action[100];
  char line_buffer[MAX_LINE_LENGTH];

  boosts = boosts;                       /* Prevent warning "unused variable" */
  fgets(line_buffer, MAX_LINE_LENGTH, stdin);      /* Read gas level at Start */
  sscanf(line_buffer, "%d %d %d", &width, &height, &gasLevel);
  fprintf(stderr, "=== >Map< ===\n");
  fprintf(stderr, "Size %d x %d\n", width, height);
  fprintf(stderr, "Gas at start %d \n\n", gasLevel);
  gwidth = width;
  gheight = height;
  for (row = 0; row < height; ++row) {
    int col;
    fgets(line_buffer, MAX_LINE_LENGTH, stdin);
    for (col = 0; col < width; col++) {
      char c = line_buffer[col];
      if (c == '1' || c == '2' || c == '3')
        gmap[row][col] = '#';
      else
        gmap[row][col] = c;
    }
    gmap[row][width] = '\0';
  }
  fflush(stderr);
  fprintf(stderr, "\n=== Race start ===\n");
  while (!feof(stdin)) {
    int secondX, secondY, thirdX, thirdY;
    round++;
    fprintf(stderr, "=== ROUND %d\n", round);
    fflush(stderr);
    fgets(line_buffer, MAX_LINE_LENGTH, stdin);   /* Read positions of pilots */
    sscanf(line_buffer, "%d %d %d %d %d %d",
           &myX, &myY, &secondX, &secondY, &thirdX, &thirdY);
    fprintf(stderr, "    Positions: Me(%d,%d)  A(%d,%d), B(%d,%d)\n",
            myX, myY, secondX, secondY, thirdX, thirdY);
    fflush(stderr);
    /* Gas consumption cannot be accurate here. */
    gasLevel += gasConsumption(accelerationX, accelerationY, speedX, speedY, gmap[myY][myX] == '~');
    speedX += accelerationX;
    speedY += accelerationY;
    /* Write the acceleration request to the race manager (stdout). */
    sprintf(action, "%d %d", accelerationX, accelerationY);
    fprintf(stdout, "%s", action);
    fflush(stdout);                           /* CAUTION : This is necessary  */
    fprintf(stderr, "    Action: %s   Gas remaining: %d\n", action, gasLevel);
    fflush(stderr);
  }

  return EXIT_SUCCESS;
}
