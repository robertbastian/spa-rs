// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>.
// This file may not be copied, modified, or distributed
// except according to those terms.

//! This example needs to be run with the `std` and `chrono` features.

use chrono::{DateTime, NaiveDate, NaiveTime};
use spa::{sunrise_and_set, StdFloatOps, SunriseAndSet};

fn main() {
    // test-vector from http://lexikon.astronomie.info/zeitgleichung/neu.html
    let tz = chrono_tz::Europe::Berlin;
    let dt = NaiveDate::from_ymd_opt(2005, 9, 30)
        .unwrap()
        .and_time(NaiveTime::from_hms_opt(12, 0, 0).unwrap())
        .and_local_timezone(tz)
        .single()
        .unwrap();

    // geo-pos near Frankfurt/Germany
    let lat = 50.0;
    let lon = 10.0;

    match sunrise_and_set::<StdFloatOps>(dt.into(), lat, lon).unwrap() {
        SunriseAndSet::Daylight(sunrise, sunset) => {
            let sunrise = DateTime::from(sunrise).with_timezone(&tz);
            let sunset = DateTime::from(sunset).with_timezone(&tz);

            println!("Sunrise and set: {} ----> {}", sunrise, sunset)
        }
        SunriseAndSet::PolarDay | SunriseAndSet::PolarNight => panic!(),
    }
}
