#![allow(dead_code, unused_mut)]
use {
    std::sync::Arc,
    tokio::{
        sync::mpsc::{self, Sender},
        time::Instant,
    }, // tokio_stream::{self as stream, StreamExt},
};

const LIMIT: usize = 30_000_000;
const BUFF_SIZE: usize = 10;
const NUM_WORKERS: usize = 3;

#[tokio::main]
async fn main() -> Result<(), ()> {
    let now = Instant::now();
    let _ = main2().await;
    let finished = Instant::now();
    println!("{:.3}", ((finished - now).as_millis() as f64) / 1000.0_f64);
    Ok(())
}

async fn main2() -> Result<(), ()> {
    // let future = helloworld();
    let dict = Arc::new(Box::new(build_dict()));
    let values = Arc::new(Box::new(build_sequence()));

    // channels
    // let (mut data_in, mut data_out) = mpsc::channel::<usize>(BUFF_SIZE);

    let (mut result_in, mut result_out) = mpsc::channel::<isize>(BUFF_SIZE);

    // receiver
    let mut pool = Vec::new();
    for i in 0..NUM_WORKERS {
        let dict1 = dict.clone();
        let result_in1 = result_in.clone();
        let values1 = values.clone();
        pool.push(tokio::spawn(async move {
            let _ = evaluator(i, values1, result_in1, dict1).await;
        }));
    }
    // let dict2 = dict.clone();
    // let result_in2 = result_in.clone();
    // let values2 = values.clone();
    // let t2 = tokio::spawn(async move {
    //     let _ = evaluator(1, values2, result_in2, dict2).await;
    // });
    // let dict3 = dict.clone();
    // let result_in3 = result_in.clone();
    // let values3 = values.clone();
    // let t3 = tokio::spawn(async move {
    //     let _ = evaluator(2, values3, result_in3, dict3).await;
    // });
    // let dict4 = dict.clone();
    // let result_in4 = result_in.clone();
    // let values4 = values.clone();
    // let t4 = tokio::spawn(async move {
    //     let _ = evaluator(3, values4, result_in4, dict4).await;
    // });

    let mut total = 0;
    for (_, _) in values.iter().enumerate() {
        let r = result_out.recv().await.unwrap();
        total += r;
    }
    println!(" - {total}");
    // future.await;
    for w in pool.iter_mut() {
        let _ = w.await.unwrap();
    }
    // let _ = t2.await.unwrap();
    // let _ = t3.await.unwrap();
    // let _ = t4.await.unwrap();
    Ok(())
}

async fn evaluator(
    nth: usize,
    input: Arc<Box<Vec<usize>>>,
    output: Sender<isize>,
    dict: Arc<Box<Vec<usize>>>,
) -> Result<(), ()> {
    let mut i = nth;
    println!("process{nth}: start");
    while i < input.len() {
        let val = input[i];
        let r = if let Some((i, _)) = dict.iter().enumerate().find(|entry| *(entry.1) == val) {
            i as isize
        } else {
            -1_isize
        };
        output.send(r).await.unwrap();
        if i == input.len() / 2 + nth {
            println!("process{nth}: half");
        }
        i += NUM_WORKERS;
    }
    println!("process{nth}: done");
    return Ok(());
}

async fn helloworld() {
    println!("hello world!");
}

fn build_sequence() -> Vec<usize> {
    let mut vec = vec![0; LIMIT];
    for (i, p) in vec.iter_mut().enumerate() {
        *p = (usize::next_power_of_two(i)) % ((usize::count_ones(i) + 3) as usize)
            * ((i * i) % (usize::count_zeros(i) as usize / 2));
    }
    vec
}

fn build_dict() -> Vec<usize> {
    let mut vec = vec![0; LIMIT / 10];
    let mut pre = 0;
    for (i, p) in vec.iter_mut().enumerate() {
        *p = (usize::next_power_of_two(i)) % ((usize::count_ones(i + 3) + 1) as usize)
            * ((i * i) % (usize::count_zeros(i) as usize));
        if pre == 0 {
            *p = i;
        } else {
            *p = (*p + pre) % 256;
        }
        pre = *p;
    }
    vec
}

fn main1() -> Result<(), ()> {
    let dict = build_dict();
    let values = build_sequence();
    println!("Hello, world: {:?}!", &dict[6400..6580]);
    println!("Hello, world: {:?}!", &values[6400..6580]);
    let x: isize = values
        .iter()
        .map(|x| {
            if let Some((i, _)) = dict.iter().enumerate().find(|entry| entry.1 == x) {
                i as isize
            } else {
                -1_isize
            }
        })
        .sum();
    println!("{x}");
    Ok(())
}
