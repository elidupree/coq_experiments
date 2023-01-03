#[actix_web::main]
async fn main() {
    quick_and_dirty_web_gui::launch(4986).await;
}
