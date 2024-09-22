#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#define MAX_THREADS 10
#define TIME_QUANTUM 2

typedef struct {
    int id;
    int burst_time;
    int remaining_time;
} Thread;

typedef struct {
    Thread* threads[MAX_THREADS];
    int front;
    int rear;
    int size;
} Queue;

void initQueue(Queue* q) {
    q->front = 0;
    q->rear = -1;
    q->size = 0;
}

void enqueue(Queue* q, Thread* thread) {
    if (q->size == MAX_THREADS) {
        printf("Queue is full\n");
        return;
    }
    q->rear = (q->rear + 1) % MAX_THREADS;
    q->threads[q->rear] = thread;
    q->size++;
}

Thread* dequeue(Queue* q) {
    if (q->size == 0) {
        return NULL;
    }
    Thread* thread = q->threads[q->front];
    q->front = (q->front + 1) % MAX_THREADS;
    q->size--;
    return thread;
}

void roundRobinSchedule(Thread threads[], int n) {
    Queue queue;
    initQueue(&queue);
    int time = 0;
    int completed = 0;

    for (int i = 0; i < n; i++) {
        enqueue(&queue, &threads[i]);
    }

    printf("Round Robin Scheduling (Time Quantum: %d)\n", TIME_QUANTUM);
    printf("Time | Thread | Remaining Time\n");

    while (completed < n) {
        Thread* current = dequeue(&queue);
        if (current == NULL) continue;

        int run_time = (current->remaining_time < TIME_QUANTUM) ? current->remaining_time : TIME_QUANTUM;
        current->remaining_time -= run_time;
        time += run_time;

        printf("%4d | %6d | %14d\n", time, current->id, current->remaining_time);

        if (current->remaining_time > 0) {
            enqueue(&queue, current);
        } else {
            completed++;
        }
    }
}

int main() {
    Thread threads[MAX_THREADS] = {
        {1, 10, 10},
        {2, 5, 5},
        {3, 8, 8},
        {4, 3, 3}
    };
    int n = 4;  // number of threads

    roundRobinSchedule(threads, n);

    return 0;
}