mod api;
mod options_dto;

use axum::Router;
use axum::routing::{get, post};
use tower_http::compression::CompressionLayer;
use tower_http::cors::CorsLayer;

fn main() {
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .thread_stack_size(64 * 1024 * 1024) // 64MB for deep UPLC recursion
        .build()
        .expect("Failed to build tokio runtime");

    rt.block_on(async {
        let app = Router::new()
            .route("/api/decompile", post(api::decompile_handler))
            .route("/api/health", get(api::health_handler))
            // The option panel, as data — the frontend renders from
            // this instead of keeping its own copy of the list.
            .route("/api/options", get(api::options_handler))
            .fallback(api::fallback_handler)
            .layer(CorsLayer::permissive())
            .layer(CompressionLayer::new());

        let port = std::env::var("PORT")
            .ok()
            .and_then(|p| p.parse::<u16>().ok())
            .unwrap_or(3000);
        let addr = format!("0.0.0.0:{}", port);
        let listener = tokio::net::TcpListener::bind(&addr)
            .await
            .unwrap_or_else(|e| panic!("Failed to bind to {}: {}", addr, e));

        println!("dehosk web UI: http://localhost:{}", port);

        axum::serve(listener, app).await.expect("Server error");
    });
}
