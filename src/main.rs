use std::{sync::Arc, thread, time};

mod tl2;

// メモリ読み込み用のマクロ
#[macro_export]
macro_rules! load {
    ($t:ident, $a:expr) => {
        if let Some(v) = ($t).load($a) {
            v
        } else {
            // 読み込みに失敗したらリトライ
            return tl2::STMResult::Retry;
        }
    };
}

// メモリ書き込み用マクロ
#[macro_export]
macro_rules! store {
    ($t:ident, $a:expr, $v:expr) => {
        $t.store($a, $v)
    };
}

// 哲学者の数
const NUM_PHILOSOPHERS: usize = 8;

fn try_pick_up_forks(tr: &mut tl2::WriteTrans, left: usize, right: usize) -> tl2::STMResult<bool> {
    let mut f1 = load!(tr, left); // 左の箸
    let mut f2 = load!(tr, right); // 右の箸
    let f1_0 = f1.first_mut().unwrap();
    let f2_0 = f2.first_mut().unwrap();
    if *f1_0 == 0 && *f2_0 == 0 {
        // 両方空いていれば1に設定
        *f1_0 = 1;
        *f2_0 = 1;
        store!(tr, left, f1);
        store!(tr, right, f2);
        tl2::STMResult::Ok(true)
    } else {
        // 両方取れない場合取得失敗
        tl2::STMResult::Ok(false)
    }
}

fn philosopher(stm: Arc<tl2::Stm>, n: usize) {
    // 左と右の箸用のメモリ
    let left = 8 * n;
    let right = 8 * ((n + 1) % NUM_PHILOSOPHERS);

    for _ in 0..500000 {
        // 箸を取り上げる
        while !stm
            .write_transaction(|tr| try_pick_up_forks(tr, left, right))
            .unwrap()
        {}

        // 箸を置く
        stm.write_transaction(|tr| {
            let mut f1 = load!(tr, left);
            let mut f2 = load!(tr, right);
            *f1.get_mut(0).unwrap() = 0;
            *f2.get_mut(0).unwrap() = 0;
            store!(tr, left, f1);
            store!(tr, right, f2);
            tl2::STMResult::Ok(())
        });
    }
}

// 観測者
fn observer(stm: Arc<tl2::Stm>) {
    for _ in 0..10000 {
        // 箸の現在の状態を取得
        let chopsticks = stm
            .read_transaction(|tr| {
                let mut v = [0; NUM_PHILOSOPHERS];
                for i in 0..NUM_PHILOSOPHERS {
                    v[i] = load!(tr, 8 * i)[0];
                }

                tl2::STMResult::Ok(v)
            })
            .unwrap();

        println!("{:?}", chopsticks);

        // 取り上げられている箸が奇数の場合は不正
        let mut n = 0;
        for c in &chopsticks {
            if *c == 1 {
                n += 1;
            }
        }

        if n & 1 != 0 {
            panic!("inconsistent");
        }

        // 100マイクロ秒スリープ
        let us = time::Duration::from_micros(100);
        thread::sleep(us);
    }
}

fn main() {
    let stm = Arc::new(tl2::Stm::new());
    let mut v = Vec::new();

    // 哲学者のスレッド生成
    for i in 0..NUM_PHILOSOPHERS {
        let s = stm.clone();
        let th = std::thread::spawn(move || philosopher(s, i));
        v.push(th);
    }

    // 観測者のスレッド生成
    let obs = std::thread::spawn(move || observer(stm));

    for th in v {
        th.join().unwrap();
    }

    obs.join().unwrap();
}
