use rand::Rng;
use std::collections::HashSet;

pub struct SequenceIterator {
    pool: u8,
    drawn: u8,
    current: Vec<u8>,
}

impl SequenceIterator {
    fn new(pool: u8, drawn: u8) -> SequenceIterator {
        SequenceIterator {
            pool,
            drawn,
            current: Vec::new(),
        }
    }

    pub fn init(&mut self, value: Option<Vec<u8>>) {
        self.current = Vec::new();
        if let Some(v) = value {
            for s in v.iter() {
                self.current.push(*s);
            }
        } else {
            for i in 1..=self.drawn {
                self.current.push(i);
            }
        }
    }

    fn inc(&mut self) -> Option<Vec<u8>> {
        if self.current.len() == 0 {
            // initialize and return the first item
            self.init(None);
            return Some(self.current.clone());
        }
        let v = self.current[self.drawn as usize - 1];
        if v < self.pool {
            // increase last number
            self.current[self.drawn as usize - 1] += 1;
            return Some(self.current.clone());
        }
        // check and increase prevous numbers
        let mut step = self.drawn - 1;
        let mut max_value = self.pool - 1;
        while step > 0 {
            let v = self.current[step as usize - 1];
            if v < max_value {
                self.current[step as usize - 1] += 1;
                let x = self.current[step as usize - 1];
                for i in step..self.drawn {
                    self.current[i as usize] = x + i - step + 1;
                }
                return Some(self.current.clone());
            }
            step -= 1;
            max_value -= 1;
        }
        None
    }
}

impl Iterator for SequenceIterator {
    type Item = Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inc()
    }
}

pub struct Lotto {
    pub pool: u8,
    pub drawn: u8,
    pub pick: u8,
    pub tickets: HashSet<String>,
    pub combos: HashSet<String>,
}

impl Lotto {
    /// Create a Lotto game with number of balls, balls to be drawn, and balls picked to maximize matches.
    ///
    /// # Examples
    ///
    /// ```
    /// let game = lotto::Lotto::new(49, 6, 4);
    /// assert_eq!(49, game.pool);
    /// ```
    pub fn new(pool: u8, drawn: u8, pick: u8) -> Lotto {
        Lotto {
            pool,
            drawn,
            pick,
            tickets: HashSet::new(),
            combos: HashSet::new(),
        }
    }

    /// Add a ticket to a lotto game only if it does not contain new picked ball matches, e.g.,
    /// in a 6-ball game to maximize 4-ball matches, add ticket only if it does not contain new 4-combos.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut game = lotto::Lotto::new(49, 6, 4);
    /// let ticket = vec![1, 2, 3, 4, 5, 6];
    /// game.add_ticket(&ticket);
    /// assert!(game.tickets.contains(&lotto::sequence_id(&ticket)));
    /// ```
    pub fn add_ticket(&mut self, ticket: &Vec<u8>) -> bool {
        let ticket_id = sequence_id(ticket);
        if self.tickets.contains(&ticket_id) {
            return false;
        }

        // ignore tickets with pick-combo that is already collected
        let mut seq = Vec::new();
        for s in SequenceIterator::new(self.drawn, self.pick) {
            let combo = s
                .iter()
                .map(|x| ticket[*x as usize - 1])
                .collect::<Vec<u8>>();
            let id = sequence_id(&combo);
            if self.combos.contains(&id) {
                return false;
            }
            seq.push(id);
        }

        self.tickets.insert(ticket_id);
        for s in seq.into_iter() {
            self.combos.insert(s);
        }
        true
    }

    /// Return number of matched combos in a specified ticket.
    fn matched_combo_count(&self, ticket: &Vec<u8>) -> u8 {
        let mut count: u8 = 0;
        for s in SequenceIterator::new(self.drawn, self.pick) {
            let combo = s
                .iter()
                .map(|x| ticket[*x as usize - 1])
                .collect::<Vec<u8>>();
            let id = sequence_id(&combo);
            if self.combos.contains(&id) {
                count += 1;
            }
        }
        count
    }

    /// Iterater for all possible tickets in the lotto game.
    ///
    /// # Examples
    ///
    /// ```
    /// let game = lotto::Lotto::new(49, 6, 4);
    /// let mut iter = game.iter();
    /// assert_eq!(Some(vec![1,2,3,4,5,6]), iter.next());
    /// ```
    pub fn iter(&self) -> SequenceIterator {
        SequenceIterator::new(self.pool, self.drawn)
    }

    /// Collect all tickets that does not contain duplicate pick-combos.
    /// Optionally specify permutations for the search.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut game = lotto::Lotto::new(10, 5, 3);
    /// game.collect_tickets(&[]);
    /// assert_eq!(6, game.tickets.len());
    /// assert_eq!(60, game.combos.len());
    /// ```
    pub fn collect_tickets(&mut self, permutations: &[Vec<u8>]) {
        const IDLE_COUNT: i32 = 5_000_000;
        let mut count = 0;
        for s in self.iter() {
            count += 1;
            if count > 4 * IDLE_COUNT {
                break;
            }
            if self.add_ticket(&s) {
                count = 0;
                println!(
                    "Iter add ticket {}; collected {} tickets and {} combos",
                    sequence_id(&s),
                    self.tickets.len(),
                    self.combos.len()
                );
            }
            if count > 0 && count % IDLE_COUNT == 0 {
                println!("No new ticket in {} evaluations", count);
            }
            if permutations.len() > 0 {
                for p in permutations.iter() {
                    count += 1;
                    let mut ticket = s.iter().map(|x| p[*x as usize - 1]).collect::<Vec<u8>>();
                    ticket.sort();
                    if self.add_ticket(&ticket) {
                        count = 0;
                        println!(
                            "Perm add ticket {}; collected {} tickets and {} combos",
                            sequence_id(&ticket),
                            self.tickets.len(),
                            self.combos.len()
                        );
                    }
                    if count > 0 && count % IDLE_COUNT == 0 {
                        println!("No new ticket in {} evaluations", count);
                    }
                }
            }
        }
        if permutations.len() > 0 {
            for p in permutations.iter() {
                println!("Permutation: {:?}", p);
            }
        }
    }

    pub fn random_collect_tickets(&mut self) {
        const IDLE_COUNT: i32 = 5_000_000;
        let mut count = 0;
        loop {
            count += 1;
            if count > 10 * IDLE_COUNT {
                break;
            }
            let s = random_sequence(self.pool, self.drawn);
            if self.add_ticket(&s) {
                count = 0;
                println!(
                    "Iter add ticket {}; collected {} tickets and {} combos",
                    sequence_id(&s),
                    self.tickets.len(),
                    self.combos.len()
                );
            }
            if count > 0 && count % IDLE_COUNT == 0 {
                println!("No new ticket in {} evaluations", count);
            }
        }
    }

    /// Verify that all tickets contain at least one match on the collected pick-combos.
    pub fn verify_tickets(&self) {
        let mut count = 0;
        let permutation = random_permutations(self.pool, 1);
        let p = &permutation[0];
        println!("verify with permutation {:?}", p);
        for s in self.iter() {
            let mut ticket = s.iter().map(|x| p[*x as usize - 1]).collect::<Vec<u8>>();
            ticket.sort();
            if self.matched_combo_count(&ticket) > 0 {
                println!("Found missing ticket {}", sequence_id(&ticket));
            } else {
                count += 1;
            }
        }
        println!("Verified {} winning tickets", count)
    }

    /// count tickets by matched pick-combos
    pub fn tickets_combo_matches(&self, size: u8) -> Vec<u32> {
        let mut result = vec![0u32; size as usize];
        let permutation = random_permutations(self.pool, 1);
        let p = &permutation[0];
        println!("count combo-match using permutation {:?}", p);
        let mut count = 0;
        for s in self.iter() {
            count += 1;
            let mut ticket = s.iter().map(|x| p[*x as usize - 1]).collect::<Vec<u8>>();
            ticket.sort();
            let m = self.matched_combo_count(&ticket);
            if m == 0 {
                println!(
                    "ticket {} does not match any pick-combo",
                    sequence_id(&ticket)
                );
            }
            if m < size {
                result[m as usize] += 1;
            }
            if count % 1_000_000 == 0 {
                println!(
                    "{} tickets are evaluated: {} no-match tickets, and {} 1-match tickets",
                    count, result[0], result[1]
                );
            }
        }
        println!(
            "{} tickets are evaluated: {} no-match tickets, and {} 1-match tickets",
            count, result[0], result[1]
        );
        result
    }
}

/// Generate random picks from pool of numbers.
/// 
/// # Examples
/// 
/// ```
/// let r = lotto::random_sequence(49, 6);
/// assert_eq!(6, r.len());
/// ```
pub fn random_sequence(pool: u8, pick: u8) -> Vec<u8> {
    let mut s: HashSet<u8> = HashSet::new();
    let mut rng = rand::thread_rng();
    while s.len() < pick as usize{
        let r: u8 = rng.gen_range(1..=pool);
        s.insert(r);
    }
    let mut r = s.into_iter().collect::<Vec<u8>>();
    r.sort();
    r
}

pub fn random_permutations(pool: u8, size: u16) -> Vec<Vec<u8>> {
    let mut permutations = Vec::new();
    for _ in 0..size {
        let mut p = Vec::new();
        for i in 1..=pool {
            p.push(i);
        }

        let mut rng = rand::thread_rng();
        for i in 1..=pool {
            let r: u8 = rng.gen_range(1..=pool);
            if i != r {
                let v = p[i as usize - 1];
                p[i as usize - 1] = p[r as usize - 1];
                p[r as usize - 1] = v;
            }
        }
        permutations.push(p);
    }
    permutations
}

/// Returns unique id of sequence of 2-digit numbers by concatenation.
///
/// # Examples
///
/// ```
/// let s = lotto::sequence_id(&vec![1, 2, 3]);
/// assert_eq!("010203", s);
/// ```
pub fn sequence_id(seq: &Vec<u8>) -> String {
    seq.iter()
        .map(|x| format!("{:02}", x))
        .collect::<Vec<String>>()
        .join("")
}

/// Return all combinations of choose k numbers from number range [a, b].
///
/// # Examples
///
/// choose 2 numbers from range [1, 3]:
///
/// ```
/// if let Some(v) = lotto::combination_sequence(1, 3, 2) {
///     assert_eq!(vec![vec![1, 2], vec![1, 3], vec![2, 3]], v);
/// }
/// ```
pub fn combination_sequence(from: u8, to: u8, count: u8) -> Option<Vec<Vec<u8>>> {
    if count < 1 || count > to - from + 1 {
        return None;
    }
    let mut result = Vec::new();
    for i in from..=to - count + 1 {
        if let Some(v) = combination_sequence(i + 1, to, count - 1) {
            for tail in v.iter() {
                result.push(concat_sequence(i, tail));
            }
        } else {
            result.push(vec![i]);
        }
    }
    Some(result)
}

fn concat_sequence(head: u8, tail: &Vec<u8>) -> Vec<u8> {
    let mut seq = Vec::new();
    seq.push(head);
    for i in tail.iter() {
        seq.push(*i);
    }
    seq
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ticket_iter_basic() {
        let game = Lotto::new(49, 6, 4);
        let mut iter = game.iter();
        for i in 6..=49 {
            if let Some(v) = iter.next() {
                assert_eq!(vec![1, 2, 3, 4, 5, i], v);
            } else {
                panic!("Failed on step {}", i);
            }
        }
    }

    #[test]
    fn test_ticket_iter_adv() {
        let game = Lotto::new(49, 6, 4);
        let mut iter = game.iter();
        iter.init(Some(vec![1, 45, 46, 47, 48, 49]));
        for i in 7..=49 {
            if let Some(v) = iter.next() {
                assert_eq!(vec![2, 3, 4, 5, 6, i], v);
            } else {
                panic!("Failed on step {}", i);
            }
        }
    }

    #[test]
    fn test_ticket_iter_last() {
        let game = Lotto::new(49, 6, 4);
        let mut iter = game.iter();
        iter.init(Some(vec![43, 45, 46, 47, 48, 49]));
        if let Some(v) = iter.next() {
            assert_eq!(vec![44, 45, 46, 47, 48, 49], v);
        } else {
            panic!("Failed on last ticket");
        }
        assert_eq!(None, iter.next(), "iter should return None after last item")
    }

    #[test]
    fn test_add_ticket() {
        let mut game = Lotto::new(49, 6, 4);
        let ticket = vec![1, 2, 3, 4, 5, 6];
        let ticket_id = sequence_id(&ticket);
        game.add_ticket(&ticket);
        assert!(
            game.tickets.contains(&ticket_id),
            "ticket {} should have been added",
            ticket_id
        );
        assert_eq!(
            15,
            game.combos.len(),
            "15 pick-4 combos should have been added"
        );
    }

    #[test]
    fn test_add_2_tickets() {
        let mut game = Lotto::new(49, 6, 4);
        let ticket = vec![1, 2, 3, 4, 5, 6];
        let ticket_id = sequence_id(&ticket);
        let ticket2 = vec![1, 2, 3, 7, 8, 9];
        let ticket_id2 = sequence_id(&ticket2);

        game.add_ticket(&ticket);
        game.add_ticket(&ticket2);
        assert!(
            game.tickets.contains(&ticket_id),
            "ticket {} should have been added",
            ticket_id
        );
        assert!(
            game.tickets.contains(&ticket_id2),
            "ticket {} should have been added",
            ticket_id2
        );
        assert_eq!(
            30,
            game.combos.len(),
            "30 pick-4 combos should have been added"
        );
    }

    #[test]
    fn test_ignored_ticket() {
        let mut game = Lotto::new(49, 6, 4);
        let ticket = vec![1, 2, 3, 4, 5, 6];
        let ticket_id = sequence_id(&ticket);
        // ticket2 contains the same pick-4 combination [1, 2, 3, 4], and it should be ignored
        let ticket2 = vec![1, 2, 3, 4, 7, 8];
        let ticket_id2 = sequence_id(&ticket2);

        game.add_ticket(&ticket);
        game.add_ticket(&ticket2);
        assert!(
            game.tickets.contains(&ticket_id),
            "ticket {} should have been added",
            ticket_id
        );
        assert!(
            !game.tickets.contains(&ticket_id2),
            "ticket {} should have been ignored",
            ticket_id2
        );
        assert_eq!(
            15,
            game.combos.len(),
            "15 pick-4 combos should have been added"
        );
    }

    #[test]
    fn test_sequence_id() {
        let s = sequence_id(&vec![1, 2, 3]);
        assert_eq!("010203", s);
    }

    #[test]
    fn choose_2_of_3() {
        if let Some(v) = combination_sequence(1, 3, 2) {
            assert_eq!(vec![vec![1, 2], vec![1, 3], vec![2, 3]], v);
        } else {
            panic!("no combination is returned");
        }
    }

    #[test]
    fn choose_3_of_3() {
        if let Some(v) = combination_sequence(1, 3, 3) {
            assert_eq!(vec![vec![1, 2, 3]], v);
        } else {
            panic!("no combination is returned");
        }
    }

    #[test]
    fn choose_4_of_3() {
        assert_eq!(None, combination_sequence(1, 3, 4));
    }
}
