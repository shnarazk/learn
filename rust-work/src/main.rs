const LIMIT: usize = 10_000_000;
#[tokio::main]
async fn main() -> Result<(), ()> {
    let dict = build_dict();
    println!("Hello, world: {:?}!", &dict[6400..6580]);
    let values = build_sequence();
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
